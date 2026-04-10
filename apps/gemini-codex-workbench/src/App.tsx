import { useState, useEffect, useRef } from 'react';
import './App.css';
import 'xterm/css/xterm.css';
import { Terminal as TerminalIcon, Copy, Send, SendHorizontal, Folder, GitBranch, ShieldAlert, File, AlertCircle, Play, Eye } from 'lucide-react';
import { Terminal } from 'xterm';
import { FitAddon } from '@xterm/addon-fit';

declare global {
  interface Window {
    electronAPI?: {
      readDir: (path: string) => Promise<ElectronEntry[]>;
      readFile: (path: string) => Promise<string>;
      gitStatus: () => Promise<string>;
      gitDiff: () => Promise<string>;
      spawnPty: () => Promise<boolean>;
      onTerminalData: (cb: (data: string) => void) => (() => void);
      sendTerminalData: (data: string) => void;
      resizeTerminal: (cols: number, rows: number) => void;
    };
  }
}

interface ElectronEntry {
  name: string;
  isDirectory: boolean;
  path: string;
}

interface TreeNodeProps {
  node: ElectronEntry;
  level: number;
  onSelectFile: (path: string) => void;
  onQuickPeek: (path: string) => void;
}

const TreeNode = ({ node, level, onSelectFile, onQuickPeek }: TreeNodeProps) => {
  const [expanded, setExpanded] = useState(false);
  const [children, setChildren] = useState<ElectronEntry[]>([]);

  const handleToggle = async (e: React.MouseEvent) => {
    e.stopPropagation();
    if (node.isDirectory) {
      if (!expanded) {
        if (window.electronAPI) {
          try {
            const kids = await window.electronAPI.readDir(node.path);
            setChildren(kids);
          } catch(e) {
            console.error(e);
          }
        }
      }
      setExpanded(!expanded);
    } else {
      onSelectFile(node.path);
    }
  };

  const handlePeek = (e: React.MouseEvent) => {
    e.stopPropagation();
    onQuickPeek(node.path);
  };

  return (
    <div>
      <div 
        onClick={handleToggle}
        style={{ 
          paddingLeft: `${level * 12 + 8}px`, 
          cursor: 'pointer', 
          display: 'flex', 
          alignItems: 'center', 
          gap: '6px',
          paddingTop: '4px',
          paddingBottom: '4px',
          paddingRight: '8px',
          position: 'relative'
        }}
        className="tree-node-hover"
      >
        {node.isDirectory ? <Folder size={12} color="#9aa0a6" style={{flexShrink: 0}} /> : <File size={12} color="#60646c" style={{flexShrink: 0}} />}
        <span style={{ overflow: 'hidden', textOverflow: 'ellipsis', whiteSpace: 'nowrap', flex: 1 }}>{node.name}</span>
        
        {!node.isDirectory && (
          <button 
            className="morphic-button peek-btn" 
            title="Quick Peek" 
            style={{ padding: '2px 4px', fontSize: '10px' }}
            onClick={handlePeek}
          >
            <Eye size={10} />
          </button>
        )}
      </div>
      {expanded && node.isDirectory && (
        <div style={{ display: 'flex', flexDirection: 'column' }}>
          {children.map(child => <TreeNode key={child.path} node={child} level={level + 1} onSelectFile={onSelectFile} onQuickPeek={onQuickPeek} />)}
        </div>
      )}
    </div>
  );
};

interface TerminalComponentProps {
  interactiveEnabled: boolean;
  isActiveTab: boolean;
}

function TerminalComponent({ interactiveEnabled, isActiveTab }: TerminalComponentProps) {
  const terminalRef = useRef<HTMLDivElement>(null);
  const termInstance = useRef<Terminal | null>(null);
  const interactiveRef = useRef(interactiveEnabled);

  useEffect(() => {
    interactiveRef.current = interactiveEnabled;
  }, [interactiveEnabled]);

  useEffect(() => {
    if (!terminalRef.current || !window.electronAPI) return;
    
    // Only mount terminal once
    if (termInstance.current) return;

    const term = new Terminal({
      fontFamily: 'var(--font-family-mono)',
      fontSize: 13,
      theme: {
        background: '#1a1a1e',
        foreground: '#e0e0e5',
      }
    });
    
    const fitAddon = new FitAddon();
    term.loadAddon(fitAddon);
    term.open(terminalRef.current);
    termInstance.current = term;

    // Slight delay to allow DOM to settle for fit
    const timeout = setTimeout(() => {
      fitAddon.fit();
      window.electronAPI!.spawnPty();
    }, 100);

    term.onData(data => {
      // Use ref to read current writeMode without remounting the terminal effect
      if (interactiveRef.current) {
        window.electronAPI!.sendTerminalData(data);
      }
    });

    const cleanupListener = window.electronAPI.onTerminalData(data => {
      term.write(data);
    });

    const handleResize = () => {
      try {
        fitAddon.fit();
        window.electronAPI!.resizeTerminal(term.cols, term.rows);
      } catch(e) {
        console.error('resize error', e);
      }
    };

    window.addEventListener('resize', handleResize);
    
    return () => {
      clearTimeout(timeout);
      window.removeEventListener('resize', handleResize);
      if (cleanupListener) {
        cleanupListener();
      }
      term.dispose();
      termInstance.current = null;
    };
  }, []);

  // Fit terminal when it becomes active again just in case window resized while hidden
  useEffect(() => {
    if (isActiveTab && termInstance.current) {
       // A small delay ensures display:block has rendered
       setTimeout(() => {
           window.dispatchEvent(new Event('resize'));
       }, 50);
    }
  }, [isActiveTab]);

  return <div ref={terminalRef} style={{ flex: 1, overflow: 'hidden', padding: '4px', backgroundColor: '#1a1a1e', borderRadius: '4px', border: '1px solid var(--color-border)' }} />;
}

interface AttachedReviewUIProps {
  attaches: ReviewRequest[];
  onView: () => void;
}

function AttachedReviewUI({ attaches, onView }: AttachedReviewUIProps) {
  if (attaches.length === 0) return null;
  return (
    <div style={{ 
      fontSize: '11px', padding: '6px 12px', marginTop: '8px', marginBottom: '8px',
      backgroundColor: 'var(--color-bg-panel)', border: '1px solid var(--color-border)', borderRadius: '4px',
      display: 'flex', justifyContent: 'space-between', alignItems: 'center'
    }}>
      <span>
        <AlertCircle size={10} style={{marginRight: '4px', verticalAlign: 'middle'}} />
        Sent for Review ({attaches.length}) &rarr; <span className="status-posture-ambiguous">{attaches[0].status}</span>
      </span>
      <button className="morphic-button" style={{padding: '2px 6px'}} onClick={onView}>View</button>
    </div>
  );
}

interface CommonViewerProps {
  onRequestReview: (kind: ReviewRequest['originKind'], id: string, scope: string) => void;
  reviewRequests: ReviewRequest[];
  onNavigateReviews: () => void;
}

function FileViewer({ activeFile, onRequestReview, reviewRequests, onNavigateReviews }: { activeFile: string | null } & CommonViewerProps) {
  const [content, setContent] = useState('');
  useEffect(() => {
    if (activeFile && window.electronAPI) {
       window.electronAPI.readFile(activeFile)
         .then(setContent)
         .catch(err => setContent("Failed to load: " + err));
    }
  }, [activeFile]);

  if (!activeFile) return <div style={{ fontSize: '13px', color: 'var(--color-text-secondary)' }}>Select a file from the workspace tree to preview it here without changing routes.</div>;

  const attaches = reviewRequests.filter(r => r.originKind === 'file' && r.originId === activeFile);

  return (
     <div style={{ position: 'relative', height: '100%', display: 'flex', flexDirection: 'column' }}>
       <div style={{ paddingBottom: '8px', flexShrink: 0, borderBottom: '1px solid var(--color-border)', marginBottom: '8px', display: 'flex', justifyContent: 'space-between', alignItems: 'center' }}>
         <div style={{ fontSize: '12px', color: 'var(--color-text-tertiary)', wordBreak: 'break-all' }}>
           {activeFile}
         </div>
         <button className="morphic-button" data-posture="advisory" onClick={() => onRequestReview('file', activeFile, activeFile)}>
           <Send size={12} /> Send Block For Review
         </button>
       </div>
       <AttachedReviewUI attaches={attaches} onView={onNavigateReviews} />
       <pre style={{ margin: 0, overflow: 'auto', flex: 1, fontSize: '13px', fontFamily: 'var(--font-family-mono)', color: 'var(--color-text-primary)' }}>
         <code>{content}</code>
       </pre>
     </div>
  );
}

function GitViewer({ mode, onRequestReview, reviewRequests, onNavigateReviews }: { mode: 'status' | 'diff' } & CommonViewerProps) {
  const [content, setContent] = useState('Fetching...');
  
  useEffect(() => {
    let active = true;
    const fetchGit = async () => {
      if (!window.electronAPI) {
        if (active) setContent('Git integration unavailable (Electron missing).');
        return;
      }
      try {
        if (mode === 'status') {
          const out = await window.electronAPI.gitStatus();
          if (active) setContent(out || 'No active changes.');
        } else {
          const out = await window.electronAPI.gitDiff();
          if (active) setContent(out || 'Diff cleanly matches HEAD.');
        }
      } catch (err) {
        if (active) setContent("Error: " + err);
      }
    };
    fetchGit();
    return () => { active = false; };
  }, [mode]);

  const originId = `git-${mode}`;
  const attaches = reviewRequests.filter(r => r.originKind === 'diff' && r.originId === originId);

  return (
    <div style={{ display: 'flex', flexDirection: 'column', height: '100%' }}>
      <div style={{ paddingBottom: '8px', flexShrink: 0, borderBottom: '1px solid var(--color-border)', marginBottom: '8px', display: 'flex', justifyContent: 'flex-end' }}>
         <button className="morphic-button" data-posture="advisory" onClick={() => onRequestReview('diff', originId, `Current Workspace ${mode}`)}>
           <Send size={12} /> Send {mode === 'status' ? 'Status' : 'Diff'} For Review
         </button>
      </div>
      <AttachedReviewUI attaches={attaches} onView={onNavigateReviews} />
      <pre style={{ margin: '0', overflow: 'auto', flex: 1, fontSize: '13px', fontFamily: 'var(--font-family-mono)', color: 'var(--color-text-primary)' }}>
        {content}
      </pre>
    </div>
  );
}

interface ChatMessage {
  id: string;
  role: 'user' | 'system';
  content: string;
}

interface ReviewRequest {
  id: string;
  originKind: 'transcript' | 'file' | 'diff';
  originId: string;
  scope: string;
  target: string;
  status: 'unavailable' | 'pending';
  posture: string;
  createdAt: number;
}

interface WorkflowRequest {
  id: string;
  template: string;
  intent: string;
  status: 'non-executed' | 'unavailable';
  posture: 'advisory';
  createdAt: number;
}

function App() {
  const [activeContextTab, setActiveContextTab] = useState<'terminal' | 'diff' | 'status' | 'files' | 'review' | 'workflows'>('terminal');
  
  // Real Local state, tracking whether writes to local processes are permitted
  const [writeMode, setWriteMode] = useState(false);

  const [rootNodes, setRootNodes] = useState<ElectronEntry[]>([]);
  const [activeFile, setActiveFile] = useState<string | null>(null);
  
  // Quick Peek State
  const [peekFile, setPeekFile] = useState<string | null>(null);

  // Chat Loop State
  const [messages, setMessages] = useState<ChatMessage[]>([]);
  const [inputValue, setInputValue] = useState('');
  
  // Review Routing State
  const [reviewRequests, setReviewRequests] = useState<ReviewRequest[]>([]);

  // Workflow State
  const [workflowRequests, setWorkflowRequests] = useState<WorkflowRequest[]>([]);

  // Scroll to bottom reference
  const transcriptRef = useRef<HTMLDivElement>(null);

  useEffect(() => {
    if (transcriptRef.current) {
       transcriptRef.current.scrollTop = transcriptRef.current.scrollHeight;
    }
  }, [messages]);

  useEffect(() => {
    if (window.electronAPI) {
      window.electronAPI.readDir('').then(setRootNodes).catch(console.error);
    }
  }, []);

  const handleSelectFile = (path: string) => {
    setActiveFile(path);
    setActiveContextTab('files');
  };
  
  const handleQuickPeek = (path: string) => {
    setPeekFile(path);
  };

  const submitMessage = () => {
    if (!inputValue.trim()) return;
    const nextMsg: ChatMessage = { id: Date.now().toString(), role: 'user', content: inputValue };
    setMessages(prev => [...prev, nextMsg]);
    setInputValue('');
    
    // Process Local response
    setTimeout(() => {
      setMessages(prev => [...prev, {
        id: (Date.now()+1).toString(),
        role: 'system',
        content: "[Response Blocked]\nADEU Codex Backend is Unconfigured/Missing.\nLocal Request Stored."
      }]);
    }, 500);
  };

  const dispatchReview = (kind: ReviewRequest['originKind'], id: string, scopeText: string) => {
    setActiveContextTab('review');
    setReviewRequests(prev => [...prev, {
      id: `req-${Date.now()}`,
      originKind: kind,
      originId: id,
      scope: scopeText.length > 100 ? scopeText.substring(0, 100) + '...' : scopeText,
      target: '[Unconfigured Backend]',
      status: 'unavailable',
      posture: 'Advisory-only',
      createdAt: Date.now()
    }]);
  };

  const dispatchWorkflow = (template: string) => {
    setActiveContextTab('workflows');
    setWorkflowRequests(prev => [...prev, {
      id: `wf-${Date.now()}`,
      template: template,
      intent: 'Execute template natively',
      status: 'unavailable',
      posture: 'advisory',
      createdAt: Date.now()
    }]);
  };

  const navigateToReviews = () => setActiveContextTab('review');

  return (
    <div className="workbench-root">
      
      {/* STATUS BOUNDARY REGION */}
      <div className="status-boundary-region" style={{ height: 'auto', minHeight: 'var(--status-bar-height)', padding: '8px 16px', flexWrap: 'wrap' }}>
        <div className="status-items">
          <button className="morphic-button" disabled title="No backend connected to start session.">Start Session</button>
          <button className="morphic-button" disabled title="No backend connected to stop.">Stop</button>
          <button className="morphic-button" disabled title="No backend connected to restart.">Restart</button>
          
          <div className="status-item" style={{marginLeft: '8px'}} title="No backend connection.">
            Session ID: <span className="status-value status-posture-ambiguous">None</span>
          </div>
          <div className="status-item" title="No backend connection.">
            Session Status: <span className="status-value status-posture-ambiguous">Offline</span>
          </div>
          <div className="status-item">
            Profile: <span className="status-value status-posture-ambiguous">Unconfigured</span>
          </div>
          <div className="status-item">
            Build/Config: <span className="status-value status-posture-ambiguous">Unknown</span>
          </div>
          <div className="status-item">
            App Server: <span className="status-value status-posture-ambiguous">Unavailable</span>
          </div>
          <div className="status-item">
            Terminal Process Writes: 
            <span className={`status-value ${writeMode ? 'status-posture-authoritative' : ''}`}>
              {writeMode ? 'ENABLED [DANGER]' : 'DISABLED (Read-Only)'}
            </span>
          </div>
        </div>
        
        <div className="status-items">
          <button 
            className="morphic-button" 
            data-posture={writeMode ? "authoritative" : "advisory"}
            onClick={() => setWriteMode(!writeMode)}
          >
            <ShieldAlert size={14} />
            {writeMode ? "Disable Writes" : "Enable Writes"}
          </button>
        </div>
      </div>

      <div className="workbench-main">
        {/* WORKSPACE REGION */}
        <div className="workspace-region" style={{ position: 'relative' }}>
          <div className="workspace-header">Workspace</div>
          <div className="workspace-content">
            <div style={{ fontSize: '13px', color: 'var(--color-text-secondary)', display: 'flex', flexDirection: 'column' }}>
              {rootNodes.map(node => (
                <TreeNode key={node.path} node={node} level={0} onSelectFile={handleSelectFile} onQuickPeek={handleQuickPeek} />
              ))}
            </div>
          </div>
          <div className="workspace-header">Recent Sessions</div>
          <div className="workspace-content">
             <div style={{ display: 'flex', flexDirection: 'column', gap: '8px', padding: '0 16px' }}>
                <div style={{ fontSize: '13px', color: 'var(--color-ambiguous)' }}>
                  [No active backend connection to pull session identifiers]
                </div>
                <div style={{ fontSize: '12px', color: 'var(--color-text-tertiary)', borderLeft: '2px solid var(--color-border)', paddingLeft: '8px' }}>
                  History tracking is completely offline. Local IDE boundaries apply natively, but no session logging exists.
                </div>
             </div>
          </div>
          
          {/* Quick Peek Overlay */}
          {peekFile && (
            <div style={{ 
              position: 'absolute', top: 40, left: 260, width: 500, height: 600, 
              backgroundColor: 'var(--color-bg-surface)', border: '1px solid var(--color-border)', 
              borderRadius: '8px', zIndex: 100, display: 'flex', flexDirection: 'column',
              boxShadow: '0 4px 12px rgba(0,0,0,0.5)'
            }}>
              <div style={{ padding: '8px 12px', borderBottom: '1px solid var(--color-border)', display: 'flex', justifyContent: 'space-between', alignItems: 'center' }}>
                <div style={{ fontSize: '12px', color: 'var(--color-text-secondary)', whiteSpace: 'nowrap', overflow: 'hidden', textOverflow: 'ellipsis', maxWidth: '80%' }}>
                  <Eye size={12} style={{marginRight: '6px', verticalAlign: 'middle'}}/>
                  {peekFile}
                </div>
                <button className="morphic-button" onClick={() => setPeekFile(null)} style={{ padding: '2px 6px' }}>Close</button>
              </div>
              <div style={{ flex: 1, overflow: 'auto', padding: '12px' }}>
                <FileViewer 
                  activeFile={peekFile} 
                  reviewRequests={reviewRequests}
                  onRequestReview={dispatchReview}
                  onNavigateReviews={navigateToReviews}
                />
              </div>
            </div>
          )}
        </div>

        {/* PRIMARY CONVERSATION REGION */}
        <div className="primary-conversation-region">
          <div className="transcript-lane" ref={transcriptRef}>
            <div className="chat-message system">
              <div className="chat-bubble">
                Local UI Boundary Spawned successfully.
                <br/><strong>Note:</strong> ADEU Backend server absent. Local operations (PTY standard shells/Git/FS Viewer) function standalone.
              </div>
            </div>
            
            {messages.map(m => {
              const attaches = reviewRequests.filter(r => r.originKind === 'transcript' && r.originId === m.id);
              return (
                <div key={m.id} className={`chat-message ${m.role}`}>
                  <div className="chat-bubble">{m.content}</div>
                  
                  <AttachedReviewUI attaches={attaches} onView={navigateToReviews} />

                  {m.role === 'system' && attaches.length === 0 && (
                    <div className="chat-actions">
                      <button className="morphic-button">
                        <Copy size={12} /> Copy
                      </button>
                      <button className="morphic-button" data-posture="advisory" onClick={() => dispatchReview('transcript', m.id, m.content)}>
                        <Send size={12} /> Send For Review
                      </button>
                    </div>
                  )}
                </div>
              );
            })}
          </div>

          <div className="composer-lane">
            <div className="composer-input-wrapper">
              <textarea 
                className="composer-input" 
                placeholder="Message local operator loop..."
                value={inputValue}
                onChange={e => setInputValue(e.target.value)}
                onKeyDown={e => {
                  if (e.key === 'Enter' && !e.shiftKey) {
                    e.preventDefault();
                    submitMessage();
                  }
                }}
              />
              <div className="composer-actions">
                <div style={{ display: 'flex', gap: '8px' }}>
                  <button className="morphic-button" onClick={() => setActiveContextTab('terminal')}>
                    <TerminalIcon size={14} /> Terminal
                  </button>
                  <button className="morphic-button" onClick={() => setActiveContextTab('diff')}>
                    <GitBranch size={14} /> Diff
                  </button>
                  <button className="morphic-button" onClick={() => setActiveContextTab('workflows')}>
                    <Play size={14} /> Workflows
                  </button>
                </div>
                <button className="morphic-button" data-posture="authoritative" onClick={submitMessage}>
                  <SendHorizontal size={14} /> Send
                </button>
              </div>
            </div>
          </div>
        </div>

        {/* CONTEXT ARTIFACT REGION */}
        <div className="context-artifact-region">
          <div className="context-header">
            <div title="Full PTY Boundary" className={`context-tab ${activeContextTab === 'terminal' ? 'active' : ''}`} onClick={() => setActiveContextTab('terminal')}>Terminal</div>
            <div title="Workspace Status" className={`context-tab ${activeContextTab === 'status' ? 'active' : ''}`} onClick={() => setActiveContextTab('status')}>Git Status</div>
            <div title="Workspace Diff" className={`context-tab ${activeContextTab === 'diff' ? 'active' : ''}`} onClick={() => setActiveContextTab('diff')}>Diff Viewer</div>
            <div title="Workspace Documents" className={`context-tab ${activeContextTab === 'files' ? 'active' : ''}`} onClick={() => setActiveContextTab('files')}>Files</div>
            <div title="Review Handoff UI" className={`context-tab ${activeContextTab === 'review' ? 'active' : ''}`} onClick={() => setActiveContextTab('review')}>Review</div>
            <div title="Workflow Triggers" className={`context-tab ${activeContextTab === 'workflows' ? 'active' : ''}`} onClick={() => setActiveContextTab('workflows')}>Workflows</div>
          </div>
          
          <div className="context-content">
            {/* TERMINAL - Do not unmount to preserve PTY shell! */}
            <div style={{ display: activeContextTab === 'terminal' ? 'flex' : 'none', flexDirection: 'column', height: '100%' }}>
              <div className={`trust-banner ${writeMode ? 'interactive' : 'readonly'}`}>
                <span>{writeMode ? 'Interactive Shell: Keystrokes transmitted.' : 'Read Only Shell: Keystrokes blocked locally.'}</span>
              </div>
              {window.electronAPI ? (
                <TerminalComponent interactiveEnabled={writeMode} isActiveTab={activeContextTab === 'terminal'} />
              ) : (
                <div style={{color: 'var(--color-ambiguous)', padding: '12px'}}>
                  Terminal inactive (not running in Electron).
                </div>
              )}
            </div>

            {activeContextTab === 'status' && (
               <GitViewer 
                mode="status" 
                reviewRequests={reviewRequests}
                onRequestReview={dispatchReview}
                onNavigateReviews={navigateToReviews}
               />
            )}
            
            {activeContextTab === 'diff' && (
               <GitViewer 
                mode="diff" 
                reviewRequests={reviewRequests}
                onRequestReview={dispatchReview}
                onNavigateReviews={navigateToReviews}
               />
            )}

            {activeContextTab === 'files' && (
              <FileViewer 
                activeFile={activeFile} 
                reviewRequests={reviewRequests}
                onRequestReview={dispatchReview}
                onNavigateReviews={navigateToReviews}
              />
            )}

            {activeContextTab === 'review' && (
               <div style={{ display: 'flex', flexDirection: 'column', gap: '8px', color: 'var(--color-text-secondary)', fontSize: '13px' }}>
                 <div style={{ display: 'flex', alignItems: 'center', gap: '6px', color: 'var(--color-text-primary)', marginBottom: '8px' }}>
                    <AlertCircle size={16} /> Review Routing Boundary
                 </div>
                 
                 {reviewRequests.length === 0 ? (
                   <div style={{ color: 'var(--color-text-tertiary)' }}>No reviews dispatched.</div>
                 ) : (
                   reviewRequests.map(r => (
                     <div key={r.id} style={{ border: '1px solid var(--color-border)', borderRadius: '6px', padding: '12px', backgroundColor: 'var(--color-bg-surface)'}}>
                        <div style={{display: 'flex', justifyContent: 'space-between', marginBottom: '8px'}}>
                          <strong style={{color: 'var(--color-text-primary)'}}>ID: {r.id}</strong>
                          <span className="status-posture-ambiguous" style={{ textTransform: 'uppercase', fontSize: '11px' }}>{r.status}</span>
                        </div>
                        <div style={{ marginBottom: '8px', display: 'flex', gap: '16px' }}>
                          <div>
                            <span style={{color: 'var(--color-text-tertiary)'}}>Target: </span> 
                            <span className="status-posture-ambiguous">{r.target}</span>
                          </div>
                          <div>
                            <span style={{color: 'var(--color-text-tertiary)'}}>Origin: </span> 
                            <span style={{color: 'var(--color-text-primary)'}}>{r.originKind}</span>
                          </div>
                        </div>
                        <div style={{ marginBottom: '8px' }}>
                          <span style={{color: 'var(--color-text-tertiary)'}}>Posture: </span> 
                          <span className="status-posture-advisory">{r.posture}</span>
                        </div>
                        <div style={{ color: 'var(--color-text-tertiary)', marginBottom: '4px' }}>Scope:</div>
                        <pre style={{ backgroundColor: 'var(--color-bg-root)', padding: '8px', borderRadius: '4px', fontSize: '12px', whiteSpace: 'pre-wrap', fontFamily: 'var(--font-family-mono)' }}>
                          {r.scope}
                        </pre>
                     </div>
                   ))
                 )}
               </div>
            )}

            {activeContextTab === 'workflows' && (
               <div style={{ display: 'flex', flexDirection: 'column', gap: '8px', color: 'var(--color-text-secondary)', fontSize: '13px' }}>
                 <div style={{ display: 'flex', alignItems: 'center', gap: '6px', color: 'var(--color-text-primary)', marginBottom: '8px' }}>
                    <Play size={16} /> Workflow Context
                 </div>
                 
                 <div style={{ paddingBottom: '12px', borderBottom: '1px solid var(--color-border)', marginBottom: '12px' }}>
                   <p style={{ margin: '0 0 12px 0' }}>Launch predefined codebase actions natively into bounded lanes.</p>
                   <div style={{ display: 'flex', gap: '8px' }}>
                     <button className="morphic-button" data-posture="advisory" onClick={() => dispatchWorkflow('codegen_standard')}>
                       Run codegen_standard
                     </button>
                     <button className="morphic-button" data-posture="advisory" onClick={() => dispatchWorkflow('diagnose_lint')}>
                       Run diagnose_lint
                     </button>
                   </div>
                 </div>

                 {workflowRequests.length === 0 ? (
                   <div style={{ color: 'var(--color-text-tertiary)' }}>No workflows dispatched.</div>
                 ) : (
                   workflowRequests.map(w => (
                     <div key={w.id} style={{ border: '1px solid var(--color-border)', borderRadius: '6px', padding: '12px', backgroundColor: 'var(--color-bg-surface)'}}>
                        <div style={{display: 'flex', justifyContent: 'space-between', marginBottom: '8px'}}>
                          <strong style={{color: 'var(--color-text-primary)'}}>ID: {w.id}</strong>
                          <span className="status-posture-ambiguous" style={{ textTransform: 'uppercase', fontSize: '11px' }}>{w.status}</span>
                        </div>
                        <div style={{ marginBottom: '8px' }}>
                          <span style={{color: 'var(--color-text-tertiary)'}}>Template: </span> 
                          <span style={{color: 'var(--color-text-primary)'}}>{w.template}</span>
                        </div>
                        <div style={{ marginBottom: '8px' }}>
                          <span style={{color: 'var(--color-text-tertiary)'}}>Intent: </span> 
                          <span style={{color: 'var(--color-text-secondary)'}}>{w.intent}</span>
                        </div>
                        <div style={{ marginBottom: '8px' }}>
                          <span style={{color: 'var(--color-text-tertiary)'}}>Posture: </span> 
                          <span className="status-posture-advisory">{w.posture}</span>
                        </div>
                        <div style={{ fontSize: '11px', color: 'var(--color-ambiguous)' }}>
                          Explicitly not executed against real backend.
                        </div>
                     </div>
                   ))
                 )}
               </div>
            )}
            
          </div>
        </div>
      </div>
    </div>
  );
}

export default App;
